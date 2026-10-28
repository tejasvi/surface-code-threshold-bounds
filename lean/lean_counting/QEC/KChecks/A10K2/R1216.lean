import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4864 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4864 = true := by
  decide +kernel

theorem tot4864 : totK PA10K2 A10K2.t4864 = [0, 212919441758, 1032129625030, 1881826600815, 1306160902008, 225539379501, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows4865 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4865 = true := by
  decide +kernel

theorem tot4865 : totK PA10K2 A10K2.t4865 = [0, 533718306304, 1807884973965, 1840149581195, 519681914450, 31614405859, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4866 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4866 = true := by
  decide +kernel

theorem tot4866 : totK PA10K2 A10K2.t4866 = [0, 0, 1064178758225, 2402043059221, 1088831233418, 77248038420, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4867 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4867 = true := by
  decide +kernel

theorem tot4867 : totK PA10K2 A10K2.t4867 = [0, 405869091711, 1432583089985, 1892472885369, 972779557867, 154481227852, 5705019915, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
