import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9812 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9812 = true := by
  decide +kernel

theorem tot9812 : totK PD2M8K2 D2M8K2.t9812 = [0, 0, 209520585522, 468214200107, 185617312684, 9653832318, 0, 0] := by
  decide +kernel

theorem rows9813 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9813 = true := by
  decide +kernel

theorem tot9813 : totK PD2M8K2 D2M8K2.t9813 = [0, 0, 86118695557, 398492461596, 322742246053, 46318190191, 1206465782, 0] := by
  decide +kernel

theorem rows9814 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9814 = true := by
  decide +kernel

theorem tot9814 : totK PD2M8K2 D2M8K2.t9814 = [0, 0, 18489772576, 345138213740, 433518954574, 56467291321, 0, 0] := by
  decide +kernel

theorem rows9815 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9815 = true := by
  decide +kernel

theorem tot9815 : totK PD2M8K2 D2M8K2.t9815 = [0, 0, 218737843632, 494519004171, 186762948927, 5499230799, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
