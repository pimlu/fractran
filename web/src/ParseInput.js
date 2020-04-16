import React from 'react';
import TextField from '@material-ui/core/TextField';
import Grid from '@material-ui/core/Grid';
import Modal from '@material-ui/core/Modal';
import Typography from '@material-ui/core/Typography';
import { withStyles } from '@material-ui/core/styles';
import IconButton from '@material-ui/core/IconButton';
import Help from '@material-ui/icons/Help';


const styles = theme => ({
  container: {
    position: 'relative'
  },
  icon: {
    position: 'absolute',
    bottom: theme.spacing(3), right: 0,
  },
  modal: {
    position: 'absolute',
    width: theme.spacing(50),
    backgroundColor: theme.palette.background.paper,
    boxShadow: theme.shadows[5],
    padding: theme.spacing(4),
    top: '50%', left: '50%',
    transform: 'translate(-50%, -50%)',
    whiteSpace: 'pre-wrap'
  },
});

class ParseInput extends React.Component {
  constructor(props) {
    super(props);
    this.state = {
      open: false
    };
  }

  onChange({target}) {
    this.props.onChange(target.value);
  }

  render() {
    let {label, rule, value, error, multi, helpText, classes} = this.props;
    let {open} = this.state;
    let modalTitle = label + " Help";
    return <div className={classes.container}>
      <TextField label={label} value={value}
        onChange={e => this.onChange(e)}
        fullWidth={true}
        error={!!error}
        helperText={error ? error.message : ' '}
        multiline={multi || false}
        rows={10} />
      <IconButton className={classes.icon} aria-label={modalTitle}
        onClick={() => this.setState({open: true})}>
        <Help />
      </IconButton>
      <Modal
        aria-labelledby="modal-title"
        aria-describedby="modal-description"
        open={open}
        onClose={() => this.setState({open: false})}>
        <div className={classes.modal}>
          <Typography variant="h6" id="modal-title">
            {modalTitle}
          </Typography>
          <Typography variant="body1" id="modal-description">
            {helpText}
          </Typography>
        </div>
      </Modal>
    </div>;
  }
}
export default withStyles(styles)(ParseInput);