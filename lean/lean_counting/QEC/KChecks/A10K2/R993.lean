import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3972 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3972 = true := by
  decide +kernel

theorem tot3972 : totK PA10K2 A10K2.t3972 = [0, 0, 0, 495995687245, 1941659911127, 2056087876070, 490293100127, 12926121504, 0, 0] := by
  decide +kernel

theorem rows3973 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3973 = true := by
  decide +kernel

theorem tot3973 : totK PA10K2 A10K2.t3973 = [0, 0, 0, 562699219426, 1795602504926, 1751264981071, 611896539663, 54615487832, 0, 0] := by
  decide +kernel

theorem rows3974 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3974 = true := by
  decide +kernel

theorem tot3974 : totK PA10K2 A10K2.t3974 = [0, 0, 0, 287020209470, 1519659858471, 2182103632568, 786649906815, 56295361699, 0, 0] := by
  decide +kernel

theorem rows3975 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3975 = true := by
  decide +kernel

theorem tot3975 : totK PA10K2 A10K2.t3975 = [0, 0, 0, 0, 527786729635, 1786312187757, 1776747529130, 481847881086, 31018567651, 0] := by
  decide +kernel

end QECKChecks.A10K2
