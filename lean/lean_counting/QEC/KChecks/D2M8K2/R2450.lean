import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9800 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9800 = true := by
  decide +kernel

theorem tot9800 : totK PD2M8K2 D2M8K2.t9800 = [0, 183510976036, 454705430890, 262246783310, 23978703950, 0, 0, 0] := by
  decide +kernel

theorem rows9801 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9801 = true := by
  decide +kernel

theorem tot9801 : totK PD2M8K2 D2M8K2.t9801 = [0, 155160407276, 459893438597, 265722883684, 16994267116, 0, 0, 0] := by
  decide +kernel

theorem rows9802 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9802 = true := by
  decide +kernel

theorem tot9802 : totK PD2M8K2 D2M8K2.t9802 = [0, 0, 217412061008, 501588904586, 168165572520, 7166294683, 0, 0] := by
  decide +kernel

theorem rows9803 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9803 = true := by
  decide +kernel

theorem tot9803 : totK PD2M8K2 D2M8K2.t9803 = [0, 84862533686, 297936738858, 377570355266, 113256322301, 4906626486, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
