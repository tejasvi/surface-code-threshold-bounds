import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12324 = true := by
  decide +kernel

theorem tot12324 : totK PD2M8K2 D2M8K2.t12324 = [180125968639, 454072480179, 266368937280, 27828660457, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12325 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12325 = true := by
  decide +kernel

theorem tot12325 : totK PD2M8K2 D2M8K2.t12325 = [156482186594, 449924352787, 275573752546, 17879893369, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12326 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12326 = true := by
  decide +kernel

theorem tot12326 : totK PD2M8K2 D2M8K2.t12326 = [0, 226878867451, 493926341162, 162042962199, 5768874209, 0, 0, 0] := by
  decide +kernel

theorem rows12327 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12327 = true := by
  decide +kernel

theorem tot12327 : totK PD2M8K2 D2M8K2.t12327 = [86527685341, 285756267986, 373419128284, 131767736038, 7481811052, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
