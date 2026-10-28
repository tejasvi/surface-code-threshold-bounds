import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6544 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6544 = true := by
  decide +kernel

theorem tot6544 : totK PA10K2 A10K2.t6544 = [0, 0, 0, 530480616720, 1832582099887, 1788893404920, 431225404478, 30953568651, 0, 0] := by
  decide +kernel

theorem rows6545 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6545 = true := by
  decide +kernel

theorem tot6545 : totK PA10K2 A10K2.t6545 = [0, 0, 0, 134178111748, 1327882477722, 2249418184341, 780396664149, 58335300251, 0, 0] := by
  decide +kernel

theorem rows6546 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6546 = true := by
  decide +kernel

theorem tot6546 : totK PA10K2 A10K2.t6546 = [0, 0, 511028321977, 1545991894174, 1319878371282, 819283512853, 596237298885, 135940379984, 5982052406, 0] := by
  decide +kernel

theorem rows6547 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6547 = true := by
  decide +kernel

theorem tot6547 : totK PA10K2 A10K2.t6547 = [0, 0, 507955215705, 1773393449010, 1896353722940, 705029505878, 70212109725, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
