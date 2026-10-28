import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5872 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5872 = true := by
  decide +kernel

theorem tot5872 : totK PD2M8K2 D2M8K2.t5872 = [0, 177692931701, 456200514162, 269232108422, 26012142351, 0, 0, 0] := by
  decide +kernel

theorem rows5873 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5873 = true := by
  decide +kernel

theorem tot5873 : totK PD2M8K2 D2M8K2.t5873 = [0, 172994979028, 477136154699, 240520178741, 12231796398, 0, 0, 0] := by
  decide +kernel

theorem rows5874 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5874 = true := by
  decide +kernel

theorem tot5874 : totK PD2M8K2 D2M8K2.t5874 = [0, 160824170644, 445660785743, 275872398181, 26504783573, 0, 0, 0] := by
  decide +kernel

theorem rows5875 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5875 = true := by
  decide +kernel

theorem tot5875 : totK PD2M8K2 D2M8K2.t5875 = [0, 181450047467, 459985983643, 237103213071, 16254766438, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
