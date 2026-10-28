import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7292 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7292 = true := by
  decide +kernel

theorem tot7292 : totK PA10K2 A10K2.t7292 = [0, 0, 0, 486327227392, 1865848927483, 2018737907953, 552448370778, 22108643497, 0, 0] := by
  decide +kernel

theorem rows7293 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7293 = true := by
  decide +kernel

theorem tot7293 : totK PA10K2 A10K2.t7293 = [0, 0, 0, 225433601318, 1256175156116, 2127610881486, 1183202073328, 140900683606, 0, 0] := by
  decide +kernel

theorem rows7294 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7294 = true := by
  decide +kernel

theorem tot7294 : totK PA10K2 A10K2.t7294 = [0, 0, 0, 0, 588702424240, 2060716487250, 1861388923714, 366029620490, 12132367858, 0] := by
  decide +kernel

theorem rows7295 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7295 = true := by
  decide +kernel

theorem tot7295 : totK PA10K2 A10K2.t7295 = [0, 0, 428122261071, 1391660659468, 1348336093421, 596863835240, 693825713779, 444380568510, 48886019071, 0] := by
  decide +kernel

end QECKChecks.A10K2
