import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4380 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4380 = true := by
  decide +kernel

theorem tot4380 : totK PA10K2 A10K2.t4380 = [0, 0, 603431051509, 1944909458764, 1871381553554, 487909027746, 18332296138, 0, 0, 0] := by
  decide +kernel

theorem rows4381 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4381 = true := by
  decide +kernel

theorem tot4381 : totK PA10K2 A10K2.t4381 = [0, 0, 361515352098, 1698405805686, 2103621342821, 582809445429, 32442760180, 0, 0, 0] := by
  decide +kernel

theorem rows4382 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4382 = true := by
  decide +kernel

theorem tot4382 : totK PA10K2 A10K2.t4382 = [0, 113616355882, 251529917496, 788939765315, 1987629123320, 1267842304397, 205801519208, 6121173289, 0, 0] := by
  decide +kernel

theorem rows4383 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4383 = true := by
  decide +kernel

theorem tot4383 : totK PA10K2 A10K2.t4383 = [0, 466140543843, 1843268282774, 1966329894666, 475359754200, 25686058060, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
