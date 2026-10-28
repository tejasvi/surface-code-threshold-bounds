import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4828 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4828 = true := by
  decide +kernel

theorem tot4828 : totK PA10K2 A10K2.t4828 = [0, 744388744904, 2218187741278, 1506916196588, 183826580953, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4829 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4829 = true := by
  decide +kernel

theorem tot4829 : totK PA10K2 A10K2.t4829 = [625789152892, 1967323155569, 1733056164235, 574104240765, 117122059515, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4830 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4830 = true := by
  decide +kernel

theorem tot4830 : totK PA10K2 A10K2.t4830 = [0, 696002003061, 2173571665751, 1799890803896, 330982981301, 6853348008, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4831 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4831 = true := by
  decide +kernel

theorem tot4831 : totK PA10K2 A10K2.t4831 = [0, 575957811809, 1902546894517, 1870346835688, 566964721261, 42701905804, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
