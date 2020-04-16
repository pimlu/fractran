import React from 'react';
import Button from '@material-ui/core/Button';
import Tooltip from '@material-ui/core/Tooltip';
import Menu from '@material-ui/core/Menu';
import MenuItem from '@material-ui/core/MenuItem';


class MenuButton extends React.Component {
  state = {
    anchorEl: null,
  }
  handleOpen = e => {
    this.setState({
      anchorEl: e.currentTarget,
    });
    e.currentTarget.focus();
  }
  handleClose = option => {
    this.setState({
      anchorEl: null,
    });
    if(this.props.onSelect)
      this.props.onSelect(option);
  }
  render = () => {
    const ITEM_HEIGHT = 48;

    const {text, options, tooltip} = this.props;
    const {anchorEl} = this.state;

    return (<div>
      <Tooltip title={tooltip} aria-label={tooltip} leaveDelay={500} arrow placement="left">
        <Button aria-controls="long-menu" aria-haspopup="true" onClick={this.handleOpen}>
          {text}
        </Button>
      </Tooltip>
      <Menu
        id="long-menu"
        keepMounted
        anchorEl={anchorEl}
        open={!!anchorEl}
        onClose={this.handleClose}
        PaperProps={{
          style: {
            maxHeight: ITEM_HEIGHT * 9.5,
            width: '40ch',
          },
        }}
      >
        {options.map((option) => (
          <MenuItem key={option} dense={true} onClick={e => this.handleClose(option)}>
            {option}
          </MenuItem>
        ))}
      </Menu>
    </div>);
  }
}

export default MenuButton;