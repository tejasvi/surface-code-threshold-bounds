import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7788 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7788 = true := by
  decide +kernel

theorem tot7788 : totK PD2M8K2 D2M8K2.t7788 = [0, 143250425163, 456759126321, 279314293982, 20220294076, 0, 0, 0] := by
  decide +kernel

theorem rows7789 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7789 = true := by
  decide +kernel

theorem tot7789 : totK PD2M8K2 D2M8K2.t7789 = [0, 150414475504, 443174886439, 278224347723, 20642848620, 0, 0, 0] := by
  decide +kernel

theorem rows7790 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7790 = true := by
  decide +kernel

theorem tot7790 : totK PD2M8K2 D2M8K2.t7790 = [0, 0, 196137299595, 483491491541, 178196088286, 9668735432, 0, 0] := by
  decide +kernel

theorem rows7791 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7791 = true := by
  decide +kernel

theorem tot7791 : totK PD2M8K2 D2M8K2.t7791 = [0, 106674435337, 357393161047, 343163099906, 83375975747, 3581949829, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
