import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows128 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t128 = true := by
  decide +kernel

theorem tot128 : totK PA10K2 A10K2.t128 = [0, 42649034548, 690085511196, 2083869501283, 1558571479975, 268232052997, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows129 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t129 = true := by
  decide +kernel

theorem tot129 : totK PA10K2 A10K2.t129 = [0, 537941208063, 1927070636364, 1836052689166, 446019897991, 25686058060, 0, 0, 0, 0] := by
  decide +kernel

theorem rows130 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t130 = true := by
  decide +kernel

theorem tot130 : totK PA10K2 A10K2.t130 = [0, 185282364397, 1093698897846, 2072085935890, 1185566420002, 204780038405, 19313972475, 0, 0, 0] := by
  decide +kernel

theorem rows131 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t131 = true := by
  decide +kernel

theorem tot131 : totK PA10K2 A10K2.t131 = [0, 203685696166, 1005941359153, 1870146190647, 1333111216740, 262536371467, 10760911071, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
