import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4052 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4052 = true := by
  decide +kernel

theorem tot4052 : totK PA10K2 A10K2.t4052 = [0, 0, 439425120013, 1419806781236, 1572933637826, 1001136461569, 412960195732, 43720954405, 0, 0] := by
  decide +kernel

theorem rows4053 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4053 = true := by
  decide +kernel

theorem tot4053 : totK PA10K2 A10K2.t4053 = [0, 0, 383097597852, 1711713438593, 2118794721993, 716253355820, 56230862260, 0, 0, 0] := by
  decide +kernel

theorem rows4054 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4054 = true := by
  decide +kernel

theorem tot4054 : totK PA10K2 A10K2.t4054 = [0, 0, 0, 461401717291, 1788545357579, 1878409319935, 507271809480, 31306924438, 0, 0] := by
  decide +kernel

theorem rows4055 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4055 = true := by
  decide +kernel

theorem tot4055 : totK PA10K2 A10K2.t4055 = [0, 0, 405501146328, 1561788540684, 2032938271902, 909064155021, 91565752760, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
