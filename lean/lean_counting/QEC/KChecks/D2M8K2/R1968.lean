import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7872 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7872 = true := by
  decide +kernel

theorem tot7872 : totK PD2M8K2 D2M8K2.t7872 = [0, 0, 192612529554, 478660136016, 231345355706, 16104584588, 0, 0] := by
  decide +kernel

theorem rows7873 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7873 = true := by
  decide +kernel

theorem tot7873 : totK PD2M8K2 D2M8K2.t7873 = [0, 0, 175608076708, 479858124352, 224499935132, 12183533023, 0, 0] := by
  decide +kernel

theorem rows7874 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7874 = true := by
  decide +kernel

theorem tot7874 : totK PD2M8K2 D2M8K2.t7874 = [0, 0, 0, 294518085504, 484031875549, 98820738219, 1162935789, 0] := by
  decide +kernel

theorem rows7875 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7875 = true := by
  decide +kernel

theorem tot7875 : totK PD2M8K2 D2M8K2.t7875 = [0, 0, 7518713851, 200659479081, 448388141814, 181248616136, 11853261585, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
