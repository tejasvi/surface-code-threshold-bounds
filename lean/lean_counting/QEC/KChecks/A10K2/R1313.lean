import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5252 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5252 = true := by
  decide +kernel

theorem tot5252 : totK PA10K2 A10K2.t5252 = [0, 117105040969, 170911960571, 537147778107, 1837583769540, 1889556295764, 505785816206, 29687484142, 0, 0] := by
  decide +kernel

theorem rows5253 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5253 = true := by
  decide +kernel

theorem tot5253 : totK PA10K2 A10K2.t5253 = [0, 466862435288, 1879821202219, 1964933429194, 477247605403, 25686058060, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5254 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5254 = true := by
  decide +kernel

theorem tot5254 : totK PA10K2 A10K2.t5254 = [0, 249468953483, 1282785643736, 2125739697297, 1021894279729, 85563439052, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5255 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5255 = true := by
  decide +kernel

theorem tot5255 : totK PA10K2 A10K2.t5255 = [0, 0, 515252642746, 1861771958670, 1800853700422, 478767813144, 30831673886, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
