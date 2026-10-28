import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows948 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t948 = true := by
  decide +kernel

theorem tot948 : totK PA10K2 A10K2.t948 = [0, 0, 0, 674363963590, 2015662752377, 1615229956433, 384923646611, 25239774317, 0, 0] := by
  decide +kernel

theorem rows949 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t949 = true := by
  decide +kernel

theorem tot949 : totK PA10K2 A10K2.t949 = [0, 0, 290974432811, 1256692047561, 1874495764052, 1097166086349, 183893538815, 5410721913, 0, 0] := by
  decide +kernel

theorem rows950 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t950 = true := by
  decide +kernel

theorem tot950 : totK PA10K2 A10K2.t950 = [0, 0, 348653493608, 1606262166088, 2055912326950, 601196252670, 37407778270, 0, 0, 0] := by
  decide +kernel

theorem rows951 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t951 = true := by
  decide +kernel

theorem tot951 : totK PA10K2 A10K2.t951 = [0, 0, 296268317924, 1213108304502, 1874119809632, 1080881018993, 172144795134, 5546304973, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
