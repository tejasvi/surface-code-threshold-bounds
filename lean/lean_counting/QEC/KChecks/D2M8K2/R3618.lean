import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14472 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14472 = true := by
  decide +kernel

theorem tot14472 : totK PD2M8K2 D2M8K2.t14472 = [158936610929, 402538324254, 280033435890, 78659705018, 3880716147, 0, 0, 0] := by
  decide +kernel

theorem rows14473 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14473 = true := by
  decide +kernel

theorem tot14473 : totK PD2M8K2 D2M8K2.t14473 = [184890716561, 454328310129, 246993619090, 19776345701, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14474 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14474 = true := by
  decide +kernel

theorem tot14474 : totK PD2M8K2 D2M8K2.t14474 = [75459327330, 344674789719, 398632716164, 92203159819, 1267860612, 0, 0, 0] := by
  decide +kernel

theorem rows14475 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14475 = true := by
  decide +kernel

theorem tot14475 : totK PD2M8K2 D2M8K2.t14475 = [0, 218068161359, 482878542640, 179625223913, 7408476506, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
