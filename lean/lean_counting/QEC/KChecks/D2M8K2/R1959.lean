import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7836 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7836 = true := by
  decide +kernel

theorem tot7836 : totK PD2M8K2 D2M8K2.t7836 = [0, 0, 166478180780, 463470888262, 256618222402, 16566314266, 0, 0] := by
  decide +kernel

theorem rows7837 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7837 = true := by
  decide +kernel

theorem tot7837 : totK PD2M8K2 D2M8K2.t7837 = [0, 0, 0, 277668442853, 491326304053, 122183006849, 4009909289, 0] := by
  decide +kernel

theorem rows7838 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7838 = true := by
  decide +kernel

theorem tot7838 : totK PD2M8K2 D2M8K2.t7838 = [0, 0, 141147496793, 369995845020, 314192824758, 67939527735, 1149959346, 0] := by
  decide +kernel

theorem rows7839 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7839 = true := by
  decide +kernel

theorem tot7839 : totK PD2M8K2 D2M8K2.t7839 = [0, 0, 155922902357, 433969901452, 283514228864, 30435711819, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
