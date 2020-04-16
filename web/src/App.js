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

import examples from './examples';
import FractranWorker from './fractran.worker';
import MenuButton from './MenuButton';
import ParseInput from './ParseInput';
import parser from './parser';


let styles = theme => ({
  root: {
    ...theme.mixins.gutters(),
    paddingTop: theme.spacing(),
    paddingBottom: theme.spacing(3),
    maxWidth: 600,
    margin: theme.spacing(2)+'px auto',
    [theme.breakpoints.down(600)]: {
      boxShadow: 'none',
      padding: 0,
      margin: 0
    }
  },
  inlineLbl: {
    marginTop: theme.spacing(1.5)
  },
  mbot: {
    width: theme.spacing(8),
  },
  inlineBtn: {
    marginLeft: theme.spacing(),
    marginTop: theme.spacing(2)
  },
  progress: {
    marginRight: theme.spacing(2),
    position: 'relative',
    top: theme.spacing(2)
  },
  link: {
    color: 'rgba(0, 0, 0, 0.54);',
    textDecoration: 'none'
  },
  sep: {
    margin: theme.spacing(4)+'px 0'
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


let exampleKeys = Object.keys(examples);

class App extends React.Component {
  state = {
    parsers: {
      input: parser('ProgInput'),
      fracs: parser('ProgFracs')
    },
    parserTxt: {
      input: '',
      fracs: ''
    },
    parserSt: {
      input: parser.initSt,
      fracs: parser.initSt
    },
    useCycles: true,
    cycleHist: '4',
    output: '[no output]',
    oldOutput: true,
    worker: null
  }

  componentDidMount() {
    this.loadExample('Hamming weight (small)');
  }

  loadExample(name) {
    let {input, program} = examples[name];
    this.parserChange('input', input);
    this.parserChange('fracs', program);
  }

  parserChange(key, text) {
    this.setState(state => {
      let {parsers, parserTxt, parserSt} = state;
      return {
        parserTxt: {...parserTxt, [key]: text},
        parserSt: {...parserSt, [key]: parsers[key](text)}
      }
    });
  }
  isValid() {
    let {worker, parserSt} = this.state;
    let invalid = parserSt.input.error || parserSt.fracs.error;
    return !!(worker || !invalid);
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
        output: data.err,
        oldOutput: false
      });
    }
  }

  toggleRun() {
    this.setState(state => {
      let {worker, parserSt,
        useCycles, cycleHist} = state;
      if(worker) {
        worker.terminate();
        worker = null;
      } else {
        worker = new FractranWorker();
        worker.onmessage = e => this.handleWorker(e);
        worker.postMessage({
          input: parserSt.input.parsed,
          program: parserSt.fracs.parsed,
          len: useCycles ? (+cycleHist)+1 : 0
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
    let {parserTxt, parserSt, useCycles, cycleHist,
      output, oldOutput, worker} = this.state;
    return <div>
      <Paper className={classes.root} elevation={1}>
        <Grid
          container
          direction="row"
          justify="space-between"
          alignItems="flex-start"
        >
          <MenuButton text="Load Example"
            options={exampleKeys}
            tooltip="Overwrites your program!"
            onSelect={v => this.loadExample(v)}/>
          <a className={classes.link} href="https://github.com/pimlu/fractran">
            <Typography variant="h4" gutterBottom align="right">
            Fast FRACTRAN
            </Typography>
          </a>
        </Grid>
        <ParseInput label="Input"
          value={parserTxt.input} error={parserSt.input.error}
          helpText={inputHelp}
          onChange={v => this.parserChange('input', v)} />
        <ParseInput label="Program" multi={true}
          value={parserTxt.fracs} error={parserSt.fracs.error}
          helpText={programHelp}
          onChange={v => this.parserChange('fracs', v)} />
        <Grid container>
            <FormControlLabel
              className={classes.inlineLbl}
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
              disabled={!this.isValid()}
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