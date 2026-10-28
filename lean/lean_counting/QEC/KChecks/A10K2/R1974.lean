import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7896 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7896 = true := by
  decide +kernel

theorem tot7896 : totK PA10K2 A10K2.t7896 = [0, 0, 492752704009, 1822742456431, 2021331929430, 612184243003, 35639371221, 0, 0, 0] := by
  decide +kernel

theorem rows7897 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7897 = true := by
  decide +kernel

theorem tot7897 : totK PA10K2 A10K2.t7897 = [0, 0, 122360162702, 1013032052132, 2135175805461, 1486968434046, 247012151628, 6281495166, 0, 0] := by
  decide +kernel

theorem rows7898 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7898 = true := by
  decide +kernel

theorem tot7898 : totK PA10K2 A10K2.t7898 = [0, 0, 0, 570211626296, 2057220351634, 1946028250975, 435321118931, 12813073358, 0, 0] := by
  decide +kernel

theorem rows7899 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7899 = true := by
  decide +kernel

theorem tot7899 : totK PA10K2 A10K2.t7899 = [0, 470692968618, 1520597896108, 1440335313038, 539838806586, 501007859663, 337104436601, 43287591117, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
