import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5752 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5752 = true := by
  decide +kernel

theorem tot5752 : totK PD2M8K2 D2M8K2.t5752 = [0, 140206794479, 437225446682, 290709085189, 22958998393, 0, 0, 0] := by
  decide +kernel

theorem rows5753 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5753 = true := by
  decide +kernel

theorem tot5753 : totK PD2M8K2 D2M8K2.t5753 = [0, 0, 211285843343, 479004707237, 168433910388, 9602367571, 0, 0] := by
  decide +kernel

theorem rows5754 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5754 = true := by
  decide +kernel

theorem tot5754 : totK PD2M8K2 D2M8K2.t5754 = [0, 106188750859, 346185227271, 340524907737, 87120033144, 3581949829, 0, 0] := by
  decide +kernel

theorem rows5755 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5755 = true := by
  decide +kernel

theorem tot5755 : totK PD2M8K2 D2M8K2.t5755 = [0, 168421041467, 435689159558, 268209967773, 27425458298, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
