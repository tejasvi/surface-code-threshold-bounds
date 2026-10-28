import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16156 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16156 = true := by
  decide +kernel

theorem tot16156 : totK PD2M8K2 D2M8K2.t16156 = [0, 0, 71435426167, 352541632914, 386452861810, 75567810848, 1162935789, 0] := by
  decide +kernel

theorem rows16157 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16157 = true := by
  decide +kernel

theorem tot16157 : totK PD2M8K2 D2M8K2.t16157 = [0, 0, 0, 211171816682, 467789734498, 158110984877, 7639145296, 0] := by
  decide +kernel

theorem rows16158 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16158 = true := by
  decide +kernel

theorem tot16158 : totK PD2M8K2 D2M8K2.t16158 = [0, 0, 163032137786, 455904705290, 255981809092, 23292940107, 0, 0] := by
  decide +kernel

theorem rows16159 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16159 = true := by
  decide +kernel

theorem tot16159 : totK PD2M8K2 D2M8K2.t16159 = [0, 0, 159575551837, 458768875078, 259566487183, 15142107619, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
