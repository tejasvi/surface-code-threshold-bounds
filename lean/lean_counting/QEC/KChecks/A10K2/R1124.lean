import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4496 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4496 = true := by
  decide +kernel

theorem tot4496 : totK PA10K2 A10K2.t4496 = [0, 446840294253, 1639284102583, 1890733114180, 767167845265, 81833488170, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4497 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4497 = true := by
  decide +kernel

theorem tot4497 : totK PA10K2 A10K2.t4497 = [0, 280605670194, 1461802847638, 2075624222162, 769160491926, 44995361554, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4498 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4498 = true := by
  decide +kernel

theorem tot4498 : totK PA10K2 A10K2.t4498 = [0, 255642388011, 1069223144585, 1988380582423, 1206493460777, 181589179945, 6239673734, 0, 0, 0] := by
  decide +kernel

theorem rows4499 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4499 = true := by
  decide +kernel

theorem tot4499 : totK PA10K2 A10K2.t4499 = [0, 486846061507, 1873751486023, 1951442885596, 552307767664, 31516126070, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
