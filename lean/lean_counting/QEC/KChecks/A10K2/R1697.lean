import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6788 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6788 = true := by
  decide +kernel

theorem tot6788 : totK PA10K2 A10K2.t6788 = [246884555525, 1170928054875, 1965235221734, 1095190913473, 175743278061, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6789 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6789 = true := by
  decide +kernel

theorem tot6789 : totK PA10K2 A10K2.t6789 = [502507968106, 1889049505180, 2093001848435, 620112654885, 44218942306, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6790 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6790 = true := by
  decide +kernel

theorem tot6790 : totK PA10K2 A10K2.t6790 = [82670484671, 888330850905, 2158464464532, 1623441561861, 295435032037, 6853348008, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6791 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6791 = true := by
  decide +kernel

theorem tot6791 : totK PA10K2 A10K2.t6791 = [0, 513006889585, 1968263375399, 2122627521422, 561631199623, 18811612322, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
