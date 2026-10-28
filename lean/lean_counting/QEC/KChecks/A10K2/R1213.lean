import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4852 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4852 = true := by
  decide +kernel

theorem tot4852 : totK PA10K2 A10K2.t4852 = [464557879428, 1805003468672, 2052551164153, 628031999124, 24417655377, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4853 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4853 = true := by
  decide +kernel

theorem tot4853 : totK PA10K2 A10K2.t4853 = [0, 508014744162, 1877525801530, 1907473664451, 496959409812, 25351274858, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4854 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4854 = true := by
  decide +kernel

theorem tot4854 : totK PA10K2 A10K2.t4854 = [456526259209, 1662453759432, 2017050658376, 798425331597, 89798761372, 5459593153, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4855 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4855 = true := by
  decide +kernel

theorem tot4855 : totK PA10K2 A10K2.t4855 = [137167096637, 1055040749276, 2152565312750, 1470725668183, 262180504184, 6853348008, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
