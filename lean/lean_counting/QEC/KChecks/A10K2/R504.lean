import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2016 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2016 = true := by
  decide +kernel

theorem tot2016 : totK PA10K2 A10K2.t2016 = [0, 0, 581341127477, 1981933447389, 1808576540812, 420734973609, 18820728501, 0, 0, 0] := by
  decide +kernel

theorem rows2017 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2017 = true := by
  decide +kernel

theorem tot2017 : totK PA10K2 A10K2.t2017 = [0, 0, 119585100515, 961825443137, 2062840504038, 1436791930804, 278077018438, 12219140272, 0, 0] := by
  decide +kernel

theorem rows2018 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2018 = true := by
  decide +kernel

theorem tot2018 : totK PA10K2 A10K2.t2018 = [0, 0, 280714159330, 1293639941294, 2074196171812, 1212826733589, 136359239778, 0, 0, 0] := by
  decide +kernel

theorem rows2019 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2019 = true := by
  decide +kernel

theorem tot2019 : totK PA10K2 A10K2.t2019 = [0, 0, 564558389173, 1862839302592, 1875214178499, 579982855002, 33678279162, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
