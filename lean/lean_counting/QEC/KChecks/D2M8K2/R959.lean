import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3836 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3836 = true := by
  decide +kernel

theorem tot3836 : totK PD2M8K2 D2M8K2.t3836 = [171303619077, 440041523832, 240546336954, 46222050096, 4431529051, 0, 0, 0] := by
  decide +kernel

theorem rows3837 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3837 = true := by
  decide +kernel

theorem tot3837 : totK PD2M8K2 D2M8K2.t3837 = [194462460500, 456896524890, 223754225312, 16620364903, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3838 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3838 = true := by
  decide +kernel

theorem tot3838 : totK PD2M8K2 D2M8K2.t3838 = [53428324476, 326310561635, 427417446339, 90186845998, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows3839 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3839 = true := by
  decide +kernel

theorem tot3839 : totK PD2M8K2 D2M8K2.t3839 = [0, 206803506514, 470716444444, 180120680406, 11752037865, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
