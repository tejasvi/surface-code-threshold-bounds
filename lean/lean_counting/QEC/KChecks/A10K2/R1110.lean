import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4440 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4440 = true := by
  decide +kernel

theorem tot4440 : totK PA10K2 A10K2.t4440 = [0, 329574811601, 1527574288968, 2191711040731, 894240552981, 73810053881, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4441 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4441 = true := by
  decide +kernel

theorem tot4441 : totK PA10K2 A10K2.t4441 = [0, 0, 575249530259, 2029570084058, 1984598075617, 453801418825, 13816090359, 0, 0, 0] := by
  decide +kernel

theorem rows4442 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4442 = true := by
  decide +kernel

theorem tot4442 : totK PA10K2 A10K2.t4442 = [0, 0, 422331448978, 1674547112195, 2043857252006, 757061148413, 69301444986, 0, 0, 0] := by
  decide +kernel

theorem rows4443 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4443 = true := by
  decide +kernel

theorem tot4443 : totK PA10K2 A10K2.t4443 = [0, 0, 478084487840, 1865407612057, 2021361242406, 544655651197, 18226519977, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
