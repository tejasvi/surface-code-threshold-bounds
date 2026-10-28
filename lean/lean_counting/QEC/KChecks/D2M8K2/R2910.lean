import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11640 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11640 = true := by
  decide +kernel

theorem tot11640 : totK PD2M8K2 D2M8K2.t11640 = [48334856787, 326113440704, 437438576271, 90863852893, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows11641 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11641 = true := by
  decide +kernel

theorem tot11641 : totK PD2M8K2 D2M8K2.t11641 = [0, 200993039326, 478542478153, 190760790900, 11885407614, 0, 0, 0] := by
  decide +kernel

theorem rows11642 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11642 = true := by
  decide +kernel

theorem tot11642 : totK PD2M8K2 D2M8K2.t11642 = [172213901999, 458430061447, 255541456857, 25130324913, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11643 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11643 = true := by
  decide +kernel

theorem tot11643 : totK PD2M8K2 D2M8K2.t11643 = [156625363907, 428258650820, 291152951572, 31434552815, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
