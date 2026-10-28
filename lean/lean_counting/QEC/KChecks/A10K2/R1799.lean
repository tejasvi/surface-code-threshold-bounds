import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7196 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7196 = true := by
  decide +kernel

theorem tot7196 : totK PA10K2 A10K2.t7196 = [0, 0, 288483183456, 1184553547715, 1899612380494, 1175167459130, 194126698644, 5447185874, 0, 0] := by
  decide +kernel

theorem rows7197 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7197 = true := by
  decide +kernel

theorem tot7197 : totK PA10K2 A10K2.t7197 = [0, 0, 461445071300, 1839819977894, 1951500689438, 444104347101, 11323844185, 0, 0, 0] := by
  decide +kernel

theorem rows7198 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7198 = true := by
  decide +kernel

theorem tot7198 : totK PA10K2 A10K2.t7198 = [0, 0, 0, 747006632383, 2249468954767, 1473327306439, 153167361190, 0, 0, 0] := by
  decide +kernel

theorem rows7199 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7199 = true := by
  decide +kernel

theorem tot7199 : totK PA10K2 A10K2.t7199 = [0, 0, 593149538699, 1988990824215, 1870677573041, 498983882128, 81608842704, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
