import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4104 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4104 = true := by
  decide +kernel

theorem tot4104 : totK PA10K2 A10K2.t4104 = [198880611318, 1354111174789, 2188659447543, 874422123193, 60970094597, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4105 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4105 = true := by
  decide +kernel

theorem tot4105 : totK PA10K2 A10K2.t4105 = [0, 628197742041, 2066780531560, 1692942948791, 297753649165, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4106 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4106 = true := by
  decide +kernel

theorem tot4106 : totK PA10K2 A10K2.t4106 = [0, 488924530030, 1797408444116, 1958502192116, 545162546913, 31987876949, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4107 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4107 = true := by
  decide +kernel

theorem tot4107 : totK PA10K2 A10K2.t4107 = [0, 467070454902, 1790192764163, 1957931889434, 567290501527, 32911643181, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
