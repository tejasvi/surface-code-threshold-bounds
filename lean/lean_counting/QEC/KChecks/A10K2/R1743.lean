import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6972 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6972 = true := by
  decide +kernel

theorem tot6972 : totK PA10K2 A10K2.t6972 = [0, 0, 308525764274, 1434214519531, 2111446117972, 1018643047014, 106050383503, 0, 0, 0] := by
  decide +kernel

theorem rows6973 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6973 = true := by
  decide +kernel

theorem tot6973 : totK PA10K2 A10K2.t6973 = [0, 0, 487588809585, 1786047385249, 1979362345984, 641588884507, 30267025398, 0, 0, 0] := by
  decide +kernel

theorem rows6974 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6974 = true := by
  decide +kernel

theorem tot6974 : totK PA10K2 A10K2.t6974 = [0, 0, 0, 788715548212, 2225533858132, 1617963119261, 276457350800, 7047025452, 0, 0] := by
  decide +kernel

theorem rows6975 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6975 = true := by
  decide +kernel

theorem tot6975 : totK PA10K2 A10K2.t6975 = [0, 0, 540648836417, 1847604034456, 1859218735126, 638523736168, 56232317999, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
