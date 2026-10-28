import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7512 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7512 = true := by
  decide +kernel

theorem tot7512 : totK PA10K2 A10K2.t7512 = [0, 0, 360353636821, 1619237665296, 2089550617861, 802644806627, 62378768877, 0, 0, 0] := by
  decide +kernel

theorem rows7513 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7513 = true := by
  decide +kernel

theorem tot7513 : totK PA10K2 A10K2.t7513 = [0, 0, 523568283244, 1912843536886, 1941375348419, 459797307778, 12917769548, 0, 0, 0] := by
  decide +kernel

theorem rows7514 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7514 = true := by
  decide +kernel

theorem tot7514 : totK PA10K2 A10K2.t7514 = [0, 0, 0, 633733121896, 2030206379968, 1641688752535, 393426028390, 25565504801, 0, 0] := by
  decide +kernel

theorem rows7515 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7515 = true := by
  decide +kernel

theorem tot7515 : totK PA10K2 A10K2.t7515 = [0, 0, 385160669654, 1436088774058, 1777130866920, 973492387023, 172842896810, 5517381808, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
