import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5592 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5592 = true := by
  decide +kernel

theorem tot5592 : totK PA10K2 A10K2.t5592 = [0, 306130628101, 927387038722, 1068107383400, 1267998097891, 916742866913, 207269719194, 6354482628, 0, 0] := by
  decide +kernel

theorem rows5593 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5593 = true := by
  decide +kernel

theorem tot5593 : totK PA10K2 A10K2.t5593 = [0, 464557879428, 1816129286566, 2069565869088, 611042275855, 23821395696, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5594 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5594 = true := by
  decide +kernel

theorem tot5594 : totK PA10K2 A10K2.t5594 = [0, 0, 580979593936, 2013208740861, 1786889291555, 418017996411, 25351274858, 0, 0, 0] := by
  decide +kernel

theorem rows5595 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5595 = true := by
  decide +kernel

theorem tot5595 : totK PA10K2 A10K2.t5595 = [0, 390797214289, 1509256684098, 1954985315909, 971298109949, 159826440669, 5459593153, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
