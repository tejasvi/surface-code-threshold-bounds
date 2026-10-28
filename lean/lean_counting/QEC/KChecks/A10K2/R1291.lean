import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5164 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5164 = true := by
  decide +kernel

theorem tot5164 : totK PA10K2 A10K2.t5164 = [0, 0, 431843827900, 1756244650436, 1942532230994, 528634013117, 25686058060, 0, 0, 0] := by
  decide +kernel

theorem rows5165 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5165 = true := by
  decide +kernel

theorem tot5165 : totK PA10K2 A10K2.t5165 = [0, 0, 163282489813, 995739901406, 1875822622182, 1200574043672, 294817481600, 24614390653, 0, 0] := by
  decide +kernel

theorem rows5166 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5166 = true := by
  decide +kernel

theorem tot5166 : totK PA10K2 A10K2.t5166 = [0, 0, 291390219549, 1245940075384, 1884335701152, 1045483324753, 168476033811, 5460492893, 0, 0] := by
  decide +kernel

theorem rows5167 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5167 = true := by
  decide +kernel

theorem tot5167 : totK PA10K2 A10K2.t5167 = [0, 0, 448210285960, 1759563776284, 2015187471147, 533523375764, 18680094416, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
