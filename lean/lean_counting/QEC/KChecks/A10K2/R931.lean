import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3724 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3724 = true := by
  decide +kernel

theorem tot3724 : totK PA10K2 A10K2.t3724 = [0, 0, 184504210359, 974148662787, 1917220134340, 1311257227348, 241312777167, 6354482628, 0, 0] := by
  decide +kernel

theorem rows3725 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3725 = true := by
  decide +kernel

theorem tot3725 : totK PA10K2 A10K2.t3725 = [0, 0, 393689445537, 1621319971573, 2047830648695, 758345722028, 58148031486, 0, 0, 0] := by
  decide +kernel

theorem rows3726 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3726 = true := by
  decide +kernel

theorem tot3726 : totK PA10K2 A10K2.t3726 = [0, 0, 503333154511, 1798163279637, 1929399560850, 564353809518, 32846095359, 0, 0, 0] := by
  decide +kernel

theorem rows3727 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3727 = true := by
  decide +kernel

theorem tot3727 : totK PA10K2 A10K2.t3727 = [0, 0, 0, 710090656520, 2056753499060, 1635174307077, 384073556332, 25734533292, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
