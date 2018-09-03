import React from 'react';
import TextField from '@material-ui/core/TextField';
import Grid from '@material-ui/core/Grid';
import Modal from '@material-ui/core/Modal';
import Typography from '@material-ui/core/Typography';
import { withStyles } from '@material-ui/core/styles';
import IconButton from '@material-ui/core/IconButton';
import Help from '@material-ui/icons/Help';

import parser from './parser.pegjs';


const styles = theme => ({
  container: {
    position: 'relative'
  },
  icon: {
    position: 'absolute',
    bottom: theme.spacing.unit*3, right: 0,
  },
  modal: {
    position: 'absolute',
    width: theme.spacing.unit*50,
    backgroundColor: theme.palette.background.paper,
    boxShadow: theme.shadows[5],
    padding: theme.spacing.unit*4,
    top: '50%', left: '50%',
    transform: 'translate(-50%, -50%)',
    whiteSpace: 'pre-wrap'
  },
});

class ParseInput extends React.Component {
  constructor(props) {
    super(props);
    this.state = {
      open: false,
      ...this.update(props.value)
    };
  }

  update(value) {
    let parsed = null, st = {error: null};
    let {rule} = this.props;
    try {
      parsed = parser.parse(value, {startRule:rule});
    } catch(e) {
      st.error = e;
    }

    this.props.onChange(value, parsed);
    return st;
  }

  onChange({target}) {
    this.setState(this.update(target.value));
  }

  render() {
    let {label, value, multi, helpText, classes} = this.props;
    let {error, open} = this.state;
    let modalTitle = label + " Help";
    return <div className={classes.container}>
      <TextField label={label} value={value}
        onChange={e => this.onChange(e)}
        fullWidth={true}
        error={!!error}
        helperText={error ? error.message : '\u00A0'}
        multiline={multi || false}
        rows={10} />
      <IconButton className={classes.icon} aria-label={modalTitle}
        onClick={() => this.setState({open: true})}>
        <Help />
      </IconButton>
      <Modal
        aria-labelledby="simple-modal-title"
        aria-describedby="simple-modal-description"
        open={open}
        onClose={() => this.setState({open: false})}>
        <div className={classes.modal}>
          <Typography variant="title" id="modal-title">
            {modalTitle}
          </Typography>
          <Typography variant="subheading" id="simple-modal-description">
            {helpText}
          </Typography>
        </div>
      </Modal>
    </div>;
  }
}
export default withStyles(styles)(ParseInput);