import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7312 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7312 = true := by
  decide +kernel

theorem tot7312 : totK PA10K2 A10K2.t7312 = [0, 0, 218412668081, 1108585727192, 2008225499854, 1380661159941, 290178258518, 20070762815, 0, 0] := by
  decide +kernel

theorem rows7313 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7313 = true := by
  decide +kernel

theorem tot7313 : totK PA10K2 A10K2.t7313 = [0, 0, 179699916473, 892991828390, 1899512049986, 1463158424577, 289374644131, 10760911071, 0, 0] := by
  decide +kernel

theorem rows7314 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7314 = true := by
  decide +kernel

theorem tot7314 : totK PA10K2 A10K2.t7314 = [0, 0, 321590953070, 1349236797781, 1849142732755, 967797705268, 127947710384, 6034215561, 0, 0] := by
  decide +kernel

theorem rows7315 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7315 = true := by
  decide +kernel

theorem tot7315 : totK PA10K2 A10K2.t7315 = [0, 0, 493085559045, 1820608853469, 1874099226983, 521251262620, 31614405859, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
