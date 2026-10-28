import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4424 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4424 = true := by
  decide +kernel

theorem tot4424 : totK PD2M8K2 D2M8K2.t4424 = [0, 0, 120420663939, 350865204458, 342915304887, 71669456202, 1186940923, 0] := by
  decide +kernel

theorem rows4425 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4425 = true := by
  decide +kernel

theorem tot4425 : totK PD2M8K2 D2M8K2.t4425 = [0, 0, 166161577275, 439913309988, 277813355132, 30317129789, 0, 0] := by
  decide +kernel

theorem rows4426 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4426 = true := by
  decide +kernel

theorem tot4426 : totK PD2M8K2 D2M8K2.t4426 = [0, 0, 120735509721, 455507226896, 301623473430, 14371843684, 0, 0] := by
  decide +kernel

theorem rows4427 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4427 = true := by
  decide +kernel

theorem tot4427 : totK PD2M8K2 D2M8K2.t4427 = [0, 0, 0, 321517225258, 526418969565, 73096053199, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
