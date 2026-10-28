import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12836 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12836 = true := by
  decide +kernel

theorem tot12836 : totK PD2M8K2 D2M8K2.t12836 = [0, 175769294680, 433569017435, 281211375720, 30508507079, 0, 0, 0] := by
  decide +kernel

theorem rows12837 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12837 = true := by
  decide +kernel

theorem tot12837 : totK PD2M8K2 D2M8K2.t12837 = [0, 71683607021, 357471335980, 370068993945, 69318959681, 1198073392, 0, 0] := by
  decide +kernel

theorem rows12838 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12838 = true := by
  decide +kernel

theorem tot12838 : totK PD2M8K2 D2M8K2.t12838 = [0, 0, 262239992803, 484278759179, 151617178586, 8470662040, 0, 0] := by
  decide +kernel

theorem rows12839 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12839 = true := by
  decide +kernel

theorem tot12839 : totK PD2M8K2 D2M8K2.t12839 = [0, 138591533057, 354526294710, 299380202775, 87024085898, 3581949829, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
