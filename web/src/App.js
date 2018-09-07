import React from 'react';

import Grid from '@material-ui/core/Grid';

import { withStyles } from '@material-ui/core/styles';
import Paper from '@material-ui/core/Paper';
import Button from '@material-ui/core/Button';
import TextField from '@material-ui/core/TextField';
import Typography from '@material-ui/core/Typography';
import Divider from '@material-ui/core/Divider';
import CircularProgress from '@material-ui/core/CircularProgress';
import Fade from '@material-ui/core/Fade';

import FormControlLabel from '@material-ui/core/FormControlLabel';
import Checkbox from '@material-ui/core/Checkbox';


import ParseInput from './ParseInput';


let styles = theme => ({
  root: {
    ...theme.mixins.gutters(),
    paddingTop: theme.spacing.unit,
    paddingBottom: theme.spacing.unit*3,
    maxWidth: 600,
    margin: theme.spacing.unit*2+'px auto',
    [theme.breakpoints.down(600)]: {
      boxShadow: 'none',
      padding: 0,
      margin: 0
    }
  },
  mbot: {
    width: theme.spacing.unit*8,
  },
  inlineBtn: {
    height: theme.spacing.unit*3,
    marginLeft: theme.spacing.unit,
    marginTop: theme.spacing.unit*2
  },
  progress: {
    marginRight: theme.spacing.unit*2,
    position: 'relative',
    top: theme.spacing.unit*2
  },
  link: {
    textDecoration: 'none'
  },
  sep: {
    margin: theme.spacing.unit*4+'px 0'
  },
  faded: {
    opacity: 0.5
  },
  right: {
    textAlign: 'right'
  }
});

let inputHelp =' You have two options for input.  The preferred option is '+
  'factored input, where you give a list of comma separated power pairs; for '+
  'example:\n\n[2,3], [3,7] becomes 2^3*3^7 = 17496.\n\nAlternatively, you '+
  'can directly input 17496 (or even 2^3*3^7), but these inputs will be '+
  'manually factored, which will be slow for large inputs.  You can use math '+
  'expressions anywhere in place of numbers.  Yes it uses bigints.';
let programHelp = 'Programs are a list of fractions separated by newlines or '+
  'commas.  It looks a bit ugly, but you can probably guess it uses % for '+
  'fractions here.  That\'s because the expression code allows for INTEGER '+
  'divisions and I wanted to make the separation clear.\n\nSo 2/3 % 3/2 '+
  'becomes 0 % 1.';

let hammingIn = '[2, 1100001b]';
let hamming = '3*11 % 2^2*5,5 % 11,13 % 2*5,1 % 5,2 % 3,2*5 % 7,7 % 2'
  .replace(/,/g, '\n');

class App extends React.Component {
  state = {
    progIn: hammingIn,
    progFr: hamming,
    progInParsed: null,
    progFrParsed: null,
    useCycles: true,
    cycleHist: '2',
    output: '[no output]',
    oldOutput: true,
    worker: null
  }

  progInChange(progIn, progInParsed) {
    this.setState({progIn, progInParsed});
  }
  progFrChange(progFr, progFrParsed) {
    this.setState({progFr, progFrParsed});
  }
  handleChecked(name) {
    return ({target}) => this.setState({[name]: target.checked});
  }
  handleText(name) {
    return ({target}) => this.setState({[name]: target.value});
  }

  handleWorker({data}) {
    if(data.good) {
      let [iters, end] = data.out.slice(1,-1).split(',fromList ');
      end = end.slice(1,-1).replace(/\(/g, '[').replace(/\)/g, ']');
      this.setState({
        worker: null,
        output: `Ran ${iters} iterations, output: ${end}`,
        oldOutput: false
      });
    } else {
      //TODO modal
      this.setState({
        worker: null,
        output: 'Error: '+data.err,
        oldOutput: false
      });
    }
  }

  toggleRun() {
    this.setState(state => {
      let {worker, progInParsed, progFrParsed,
        useCycles, cycleHist} = state;
      if(worker) {
        worker.terminate();
        worker = null;
      } else {
        worker = new Worker('worker.js');
        worker.onmessage = e => this.handleWorker(e);
        worker.postMessage({
          input: progInParsed,
          program: progFrParsed,
          len: useCycles ? cycleHist+1 : 0
        });
      }
      return {
        oldOutput: true,
        worker
      };
    });
  }

  render() {
    let {classes} = this.props;
    let {progIn, progFr, useCycles, cycleHist,
      output, oldOutput, worker} = this.state;
    return <div>
      <Paper className={classes.root} elevation={1}>
        <a className={classes.link} href="https://github.com/pimlu/fractran">
          <Typography variant="display1" gutterBottom align="right">
           Fast FRACTRAN
          </Typography>
        </a>
        <ParseInput label="Input"
          value={progIn} rule="ProgInput"
          helpText={inputHelp}
          onChange={(i, p) => this.progInChange(i, p)} />
        <ParseInput label="Program" multi={true}
          value={progFr} rule="ProgFracs"
          helpText={programHelp}
          onChange={(i, p) => this.progFrChange(i, p)} />
          <Grid container>
            <div>
              <FormControlLabel
                control={
                  <Checkbox
                    checked={useCycles}
                    onChange={this.handleChecked('useCycles')}
                  />
                }
                label="Cycle detection"
              />
              <TextField label="Length" type="number"
                className={classes.mbot}
                margin="dense"
                value={useCycles ? cycleHist : 0}
                inputProps={{min: '1', max: '99', step: '1' }}
                disabled={!useCycles} onChange={this.handleText('cycleHist')}/>
            </div>
            <Grid item xs></Grid>
            <div className={classes.right}>
              <Fade
                in={!!worker}
                style={{
                  transitionDelay: worker ? '500ms' : '0ms',
                }}
                unmountOnExit>
                <CircularProgress className={classes.progress}
                  color="secondary" size={24} />
              </Fade>
              <Button variant="contained" className={classes.inlineBtn}
                color={worker ? 'secondary' : 'primary'}
                onClick={() => this.toggleRun()}>
                  {worker ? 'STOP' : 'RUN'}
                </Button>
            </div>
          </Grid>
          <Divider className={classes.sep}/>
          <Typography gutterBottom className={oldOutput ? classes.faded : ''}>
            {output}
          </Typography>
      </Paper>
    </div>;
  }
}
export default withStyles(styles)(App);