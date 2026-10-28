import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12008 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12008 = true := by
  decide +kernel

theorem tot12008 : totK PD2M8K2 D2M8K2.t12008 = [186113557221, 452977272367, 261482006942, 28118811702, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12009 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12009 = true := by
  decide +kernel

theorem tot12009 : totK PD2M8K2 D2M8K2.t12009 = [180570626710, 486276633153, 234991528351, 12357439692, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12010 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12010 = true := by
  decide +kernel

theorem tot12010 : totK PD2M8K2 D2M8K2.t12010 = [0, 216091745127, 459257819633, 216553430613, 21379892652, 0, 0, 0] := by
  decide +kernel

theorem rows12011 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12011 = true := by
  decide +kernel

theorem tot12011 : totK PD2M8K2 D2M8K2.t12011 = [0, 190186309750, 478354683811, 226828214405, 9369622445, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
