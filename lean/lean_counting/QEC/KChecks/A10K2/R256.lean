import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1024 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1024 = true := by
  decide +kernel

theorem tot1024 : totK PA10K2 A10K2.t1024 = [0, 0, 495602153361, 1858810540824, 1939492878000, 520025394595, 31522233512, 0, 0, 0] := by
  decide +kernel

theorem rows1025 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1025 = true := by
  decide +kernel

theorem tot1025 : totK PA10K2 A10K2.t1025 = [0, 425160027239, 1618305277416, 1996533836402, 830977992178, 82597896813, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1026 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1026 = true := by
  decide +kernel

theorem tot1026 : totK PA10K2 A10K2.t1026 = [0, 441787023334, 1773997968193, 2104479742817, 691606327243, 38691789058, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1027 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1027 = true := by
  decide +kernel

theorem tot1027 : totK PA10K2 A10K2.t1027 = [0, 0, 621675362387, 2071285755729, 1886348727708, 404040647054, 6853348008, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
