import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9004 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9004 = true := by
  decide +kernel

theorem tot9004 : totK PD2M8K2 D2M8K2.t9004 = [0, 161358637377, 445634078565, 282035543340, 26518556587, 0, 0, 0] := by
  decide +kernel

theorem rows9005 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9005 = true := by
  decide +kernel

theorem tot9005 : totK PD2M8K2 D2M8K2.t9005 = [0, 0, 275031186677, 483394086787, 106670568591, 2125526286, 0, 0] := by
  decide +kernel

theorem rows9006 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9006 = true := by
  decide +kernel

theorem tot9006 : totK PD2M8K2 D2M8K2.t9006 = [0, 153912573294, 403861925214, 275159441694, 58819725247, 2754314106, 0, 0] := by
  decide +kernel

theorem rows9007 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9007 = true := by
  decide +kernel

theorem tot9007 : totK PD2M8K2 D2M8K2.t9007 = [0, 167207202074, 440059866221, 276926035988, 28068823080, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
