import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows688 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t688 = true := by
  decide +kernel

theorem tot688 : totK PA10K2 A10K2.t688 = [0, 416581648771, 1651854649211, 1974723704432, 641275675774, 39719428504, 0, 0, 0, 0] := by
  decide +kernel

theorem rows689 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t689 = true := by
  decide +kernel

theorem tot689 : totK PA10K2 A10K2.t689 = [0, 0, 601561173985, 1958399943130, 1666623011418, 365239032724, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows690 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t690 = true := by
  decide +kernel

theorem tot690 : totK PA10K2 A10K2.t690 = [0, 378080389868, 1366585363006, 1756681630763, 999445007584, 184534989514, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows691 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t691 = true := by
  decide +kernel

theorem tot691 : totK PA10K2 A10K2.t691 = [0, 470457557640, 1847351766563, 1919267697116, 493309054406, 26521581199, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
