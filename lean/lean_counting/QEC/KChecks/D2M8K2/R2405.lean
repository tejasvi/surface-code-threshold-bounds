import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9620 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9620 = true := by
  decide +kernel

theorem tot9620 : totK PD2M8K2 D2M8K2.t9620 = [0, 0, 251407099915, 501710229961, 132841178425, 2276462501, 0, 0] := by
  decide +kernel

theorem rows9621 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9621 = true := by
  decide +kernel

theorem tot9621 : totK PD2M8K2 D2M8K2.t9621 = [0, 87204366028, 362389791107, 366424784509, 73953636585, 2896345377, 0, 0] := by
  decide +kernel

theorem rows9622 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9622 = true := by
  decide +kernel

theorem tot9622 : totK PD2M8K2 D2M8K2.t9622 = [0, 182651902662, 444465473006, 258657868497, 26998748527, 0, 0, 0] := by
  decide +kernel

theorem rows9623 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9623 = true := by
  decide +kernel

theorem tot9623 : totK PD2M8K2 D2M8K2.t9623 = [0, 144630949931, 444862612782, 283815877828, 19966400013, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
