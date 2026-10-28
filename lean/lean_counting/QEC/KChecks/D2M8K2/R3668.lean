import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14672 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14672 = true := by
  decide +kernel

theorem tot14672 : totK PD2M8K2 D2M8K2.t14672 = [0, 0, 228069318925, 477360227448, 196767615624, 15007737670, 0, 0] := by
  decide +kernel

theorem rows14673 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14673 = true := by
  decide +kernel

theorem tot14673 : totK PD2M8K2 D2M8K2.t14673 = [0, 0, 169495238992, 479736451277, 225155095968, 11837532442, 0, 0] := by
  decide +kernel

theorem rows14674 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14674 = true := by
  decide +kernel

theorem tot14674 : totK PD2M8K2 D2M8K2.t14674 = [0, 0, 191076159690, 466205858363, 223286910423, 20090775370, 0, 0] := by
  decide +kernel

theorem rows14675 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14675 = true := by
  decide +kernel

theorem tot14675 : totK PD2M8K2 D2M8K2.t14675 = [0, 0, 192277167202, 472105083911, 220666229521, 12439805748, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
