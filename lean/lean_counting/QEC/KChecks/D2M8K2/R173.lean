import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows692 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t692 = true := by
  decide +kernel

theorem tot692 : totK PD2M8K2 D2M8K2.t692 = [58180838941, 359319764394, 441738772131, 54388938718, 0, 0, 0, 0] := by
  decide +kernel

theorem rows693 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t693 = true := by
  decide +kernel

theorem tot693 : totK PD2M8K2 D2M8K2.t693 = [185335941074, 433008570888, 261386096215, 30325649102, 0, 0, 0, 0] := by
  decide +kernel

theorem rows694 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t694 = true := by
  decide +kernel

theorem tot694 : totK PD2M8K2 D2M8K2.t694 = [142746742543, 466593327362, 277256739911, 16120910468, 0, 0, 0, 0] := by
  decide +kernel

theorem rows695 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t695 = true := by
  decide +kernel

theorem tot695 : totK PD2M8K2 D2M8K2.t695 = [0, 189285853899, 433578495687, 247502764283, 25276541998, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
