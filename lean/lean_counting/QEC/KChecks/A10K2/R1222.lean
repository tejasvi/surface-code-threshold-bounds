import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4888 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4888 = true := by
  decide +kernel

theorem tot4888 : totK PA10K2 A10K2.t4888 = [0, 304239728471, 849365514109, 1001424344713, 1394552745386, 905903101160, 160162151064, 5676195732, 0, 0] := by
  decide +kernel

theorem rows4889 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4889 = true := by
  decide +kernel

theorem tot4889 : totK PA10K2 A10K2.t4889 = [0, 463275716871, 1798438435859, 2016976754648, 588001829905, 38096644685, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4890 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4890 = true := by
  decide +kernel

theorem tot4890 : totK PA10K2 A10K2.t4890 = [0, 0, 656852911502, 2088834692902, 1658952615178, 384048570289, 25313348169, 0, 0, 0] := by
  decide +kernel

theorem rows4891 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4891 = true := by
  decide +kernel

theorem tot4891 : totK PA10K2 A10K2.t4891 = [0, 455581209591, 1669389157329, 2012887446537, 800376375830, 78870212128, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
