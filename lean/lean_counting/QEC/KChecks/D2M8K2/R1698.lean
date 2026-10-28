import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6792 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6792 = true := by
  decide +kernel

theorem tot6792 : totK PD2M8K2 D2M8K2.t6792 = [0, 0, 321157607226, 519711006916, 81741682037, 0, 0, 0] := by
  decide +kernel

theorem rows6793 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6793 = true := by
  decide +kernel

theorem tot6793 : totK PD2M8K2 D2M8K2.t6793 = [0, 161132822848, 410529909206, 276032527015, 67051093523, 1415142070, 0, 0] := by
  decide +kernel

theorem rows6794 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6794 = true := by
  decide +kernel

theorem tot6794 : totK PD2M8K2 D2M8K2.t6794 = [0, 182992536418, 444794013136, 246743119171, 17611099501, 0, 0, 0] := by
  decide +kernel

theorem rows6795 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6795 = true := by
  decide +kernel

theorem tot6795 : totK PD2M8K2 D2M8K2.t6795 = [0, 81621031138, 421804303439, 368866032015, 42403421976, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
