import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3788 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3788 = true := by
  decide +kernel

theorem tot3788 : totK PA10K2 A10K2.t3788 = [0, 0, 28346906211, 544405362408, 1987928537143, 1638940069315, 303039776009, 10760911071, 0, 0] := by
  decide +kernel

theorem rows3789 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3789 = true := by
  decide +kernel

theorem tot3789 : totK PA10K2 A10K2.t3789 = [0, 0, 541634732801, 1970138693257, 1850335285501, 468588093913, 26491486257, 0, 0, 0] := by
  decide +kernel

theorem rows3790 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3790 = true := by
  decide +kernel

theorem tot3790 : totK PA10K2 A10K2.t3790 = [0, 0, 205077398441, 1208014489136, 2201053536268, 1235883657185, 194200067507, 15171143123, 0, 0] := by
  decide +kernel

theorem rows3791 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3791 = true := by
  decide +kernel

theorem tot3791 : totK PA10K2 A10K2.t3791 = [0, 0, 95362173566, 678700300856, 1812793804365, 1763326702571, 416045924537, 16597605730, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
