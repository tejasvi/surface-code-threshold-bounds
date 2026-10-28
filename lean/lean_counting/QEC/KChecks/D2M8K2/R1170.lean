import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4680 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4680 = true := by
  decide +kernel

theorem tot4680 : totK PD2M8K2 D2M8K2.t4680 = [0, 0, 198566102181, 478318375619, 221933550407, 12208674056, 0, 0] := by
  decide +kernel

theorem rows4681 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4681 = true := by
  decide +kernel

theorem tot4681 : totK PD2M8K2 D2M8K2.t4681 = [0, 54009388675, 223271032999, 431777488500, 197702536992, 8214505460, 0, 0] := by
  decide +kernel

theorem rows4682 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4682 = true := by
  decide +kernel

theorem tot4682 : totK PD2M8K2 D2M8K2.t4682 = [0, 175277725386, 445160377698, 279705647680, 28892716306, 0, 0, 0] := by
  decide +kernel

theorem rows4683 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4683 = true := by
  decide +kernel

theorem tot4683 : totK PD2M8K2 D2M8K2.t4683 = [0, 117630249627, 443996210966, 331644830723, 33011669001, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
