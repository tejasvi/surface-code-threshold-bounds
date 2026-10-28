import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows848 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t848 = true := by
  decide +kernel

theorem tot848 : totK PD2M8K2 D2M8K2.t848 = [0, 0, 200986421724, 474400083225, 220592007996, 13656771860, 0, 0] := by
  decide +kernel

theorem rows849 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t849 = true := by
  decide +kernel

theorem tot849 : totK PD2M8K2 D2M8K2.t849 = [0, 100759046162, 341571865923, 352400231765, 98799657012, 1409560813, 0, 0] := by
  decide +kernel

theorem rows850 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t850 = true := by
  decide +kernel

theorem tot850 : totK PD2M8K2 D2M8K2.t850 = [0, 194368028778, 455298444566, 236861254933, 18376726353, 0, 0, 0] := by
  decide +kernel

theorem rows851 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t851 = true := by
  decide +kernel

theorem tot851 : totK PD2M8K2 D2M8K2.t851 = [0, 26599273453, 335184250963, 444881611614, 75993885184, 1070790515, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
