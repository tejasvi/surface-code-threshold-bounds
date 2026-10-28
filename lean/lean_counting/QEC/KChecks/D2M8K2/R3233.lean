import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12932 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12932 = true := by
  decide +kernel

theorem tot12932 : totK PD2M8K2 D2M8K2.t12932 = [0, 16920019376, 265434752448, 490398661580, 126127926759, 3880716147, 0, 0] := by
  decide +kernel

theorem rows12933 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12933 = true := by
  decide +kernel

theorem tot12933 : totK PD2M8K2 D2M8K2.t12933 = [0, 197201072552, 461267431757, 240792270145, 23350948179, 0, 0, 0] := by
  decide +kernel

theorem rows12934 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12934 = true := by
  decide +kernel

theorem tot12934 : totK PD2M8K2 D2M8K2.t12934 = [0, 172942879662, 474352107175, 248824874317, 15292379483, 0, 0, 0] := by
  decide +kernel

theorem rows12935 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12935 = true := by
  decide +kernel

theorem tot12935 : totK PD2M8K2 D2M8K2.t12935 = [0, 0, 275378514324, 499304933299, 117076948650, 1267860612, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
