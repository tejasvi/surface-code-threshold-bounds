import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11588 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11588 = true := by
  decide +kernel

theorem tot11588 : totK PD2M8K2 D2M8K2.t11588 = [0, 219982989218, 489156099319, 186985890584, 7030909787, 0, 0, 0] := by
  decide +kernel

theorem rows11589 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11589 = true := by
  decide +kernel

theorem tot11589 : totK PD2M8K2 D2M8K2.t11589 = [0, 154533517381, 464816836153, 252112906513, 11661096746, 0, 0, 0] := by
  decide +kernel

theorem rows11590 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11590 = true := by
  decide +kernel

theorem tot11590 : totK PD2M8K2 D2M8K2.t11590 = [183243395725, 428205535035, 253338070137, 62482017602, 9677292770, 0, 0, 0] := by
  decide +kernel

theorem rows11591 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11591 = true := by
  decide +kernel

theorem tot11591 : totK PD2M8K2 D2M8K2.t11591 = [171813452231, 475662311473, 242336240912, 15404814044, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
