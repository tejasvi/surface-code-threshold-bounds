import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows140 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t140 = true := by
  decide +kernel

theorem tot140 : totK PA10K2 A10K2.t140 = [0, 0, 415816603413, 1729823951840, 1875819025276, 503244895186, 31810367341, 0, 0, 0] := by
  decide +kernel

theorem rows141 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t141 = true := by
  decide +kernel

theorem tot141 : totK PA10K2 A10K2.t141 = [15792662511, 0, 0, 712891715500, 2038855860301, 1412763964045, 259258309005, 6354482628, 0, 0] := by
  decide +kernel

theorem rows142 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t142 = true := by
  decide +kernel

theorem tot142 : totK PA10K2 A10K2.t142 = [532489971254, 1929879402537, 1866918894414, 439776242322, 25686058060, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows143 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t143 = true := by
  decide +kernel

theorem tot143 : totK PA10K2 A10K2.t143 = [295901161011, 1445654589109, 2177014240380, 968216194731, 82972559017, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
