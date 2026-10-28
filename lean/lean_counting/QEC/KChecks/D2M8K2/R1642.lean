import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6568 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6568 = true := by
  decide +kernel

theorem tot6568 : totK PD2M8K2 D2M8K2.t6568 = [0, 179680919003, 455214688209, 252048611303, 17664760871, 0, 0, 0] := by
  decide +kernel

theorem rows6569 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6569 = true := by
  decide +kernel

theorem tot6569 : totK PD2M8K2 D2M8K2.t6569 = [0, 72597646865, 339664499352, 378453822936, 81115585177, 1171084559, 0, 0] := by
  decide +kernel

theorem rows6570 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6570 = true := by
  decide +kernel

theorem tot6570 : totK PD2M8K2 D2M8K2.t6570 = [0, 0, 230879717473, 466319635334, 158005146426, 9444064503, 0, 0] := by
  decide +kernel

theorem rows6571 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6571 = true := by
  decide +kernel

theorem tot6571 : totK PD2M8K2 D2M8K2.t6571 = [0, 170388669167, 417132057551, 242307861987, 48997002899, 2490301335, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
