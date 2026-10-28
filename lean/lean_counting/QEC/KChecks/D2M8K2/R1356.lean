import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5424 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5424 = true := by
  decide +kernel

theorem tot5424 : totK PD2M8K2 D2M8K2.t5424 = [0, 0, 227258797202, 457963432666, 226435193390, 22910943455, 0, 0] := by
  decide +kernel

theorem rows5425 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5425 = true := by
  decide +kernel

theorem tot5425 : totK PD2M8K2 D2M8K2.t5425 = [0, 0, 93861400543, 440259149973, 337343051735, 30456890274, 0, 0] := by
  decide +kernel

theorem rows5426 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5426 = true := by
  decide +kernel

theorem tot5426 : totK PD2M8K2 D2M8K2.t5426 = [0, 0, 81123690805, 310191445290, 418981614257, 83772629645, 1394496256, 0] := by
  decide +kernel

theorem rows5427 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5427 = true := by
  decide +kernel

theorem tot5427 : totK PD2M8K2 D2M8K2.t5427 = [0, 0, 177936335313, 468993361765, 250731979356, 22739313779, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
