import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6620 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6620 = true := by
  decide +kernel

theorem tot6620 : totK PA10K2 A10K2.t6620 = [0, 0, 295617904848, 1456262915887, 2199290478122, 898893124179, 67563397186, 0, 0, 0] := by
  decide +kernel

theorem rows6621 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6621 = true := by
  decide +kernel

theorem tot6621 : totK PA10K2 A10K2.t6621 = [0, 0, 0, 545537016819, 1787261296634, 1750992352242, 483849555222, 31082886609, 0, 0] := by
  decide +kernel

theorem rows6622 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6622 = true := by
  decide +kernel

theorem tot6622 : totK PA10K2 A10K2.t6622 = [0, 0, 521968057584, 1794756330879, 1824770112435, 599620191091, 50246248178, 0, 0, 0] := by
  decide +kernel

theorem rows6623 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6623 = true := by
  decide +kernel

theorem tot6623 : totK PA10K2 A10K2.t6623 = [0, 0, 145964120466, 950578214278, 2011834072643, 1268459649893, 194994879671, 5885702948, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
