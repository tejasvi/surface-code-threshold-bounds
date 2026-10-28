import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7916 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7916 = true := by
  decide +kernel

theorem tot7916 : totK PA10K2 A10K2.t7916 = [0, 402147379209, 1724738452004, 1987112439039, 633947193238, 47481764078, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7917 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7917 = true := by
  decide +kernel

theorem tot7917 : totK PA10K2 A10K2.t7917 = [0, 373065902119, 1455945448165, 2062225100884, 967076714734, 100746996841, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7918 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7918 = true := by
  decide +kernel

theorem tot7918 : totK PA10K2 A10K2.t7918 = [0, 459706590608, 1807447874737, 2085687878549, 691849657395, 39446437729, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7919 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7919 = true := by
  decide +kernel

theorem tot7919 : totK PA10K2 A10K2.t7919 = [0, 0, 593614175995, 2049494796235, 1961430448827, 458627917703, 13814447077, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
