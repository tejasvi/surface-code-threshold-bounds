import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2076 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2076 = true := by
  decide +kernel

theorem tot2076 : totK PD2M8K2 D2M8K2.t2076 = [0, 192684241871, 469993554135, 229631354292, 15567529767, 0, 0, 0] := by
  decide +kernel

theorem rows2077 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2077 = true := by
  decide +kernel

theorem tot2077 : totK PD2M8K2 D2M8K2.t2077 = [0, 34541272259, 269595341633, 402237801349, 183420840290, 19897919922, 0, 0] := by
  decide +kernel

theorem rows2078 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2078 = true := by
  decide +kernel

theorem tot2078 : totK PD2M8K2 D2M8K2.t2078 = [0, 0, 188049355207, 483089036274, 220726478007, 6952306714, 0, 0] := by
  decide +kernel

theorem rows2079 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2079 = true := by
  decide +kernel

theorem tot2079 : totK PD2M8K2 D2M8K2.t2079 = [0, 123510007115, 346786813610, 313592822235, 115010483628, 6804944647, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
