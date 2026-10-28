import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6768 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6768 = true := by
  decide +kernel

theorem tot6768 : totK PD2M8K2 D2M8K2.t6768 = [153421184897, 460443754544, 282503215361, 22443754829, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6769 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6769 = true := by
  decide +kernel

theorem tot6769 : totK PD2M8K2 D2M8K2.t6769 = [0, 215255597088, 485059156830, 182740327719, 9562610978, 0, 0, 0] := by
  decide +kernel

theorem rows6770 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6770 = true := by
  decide +kernel

theorem tot6770 : totK PD2M8K2 D2M8K2.t6770 = [89709506736, 341199608636, 398443281117, 91024099008, 2491535930, 0, 0, 0] := by
  decide +kernel

theorem rows6771 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6771 = true := by
  decide +kernel

theorem tot6771 : totK PD2M8K2 D2M8K2.t6771 = [193522121204, 460396402187, 241548752619, 20121136234, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
